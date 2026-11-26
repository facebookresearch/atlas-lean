# Polynomial commitment schemes

A polynomial commitment lets a committer open either a whole formal polynomial or its value at a single point. These are different promises: two full openings are compared as polynomials, whereas two evaluation claims are compared at **one and the same index**.

## Operations and correctness

Kate, Zaverucha and Goldberg specify six algorithms. **Setup** on $(1^\kappa,t)$ generates a public key $k$ containing the algebraic parameters, including a prime $p$, and a secret key not needed afterwards. A message is a formal $f\in\mathbb F_p[X]$ of degree at most $t$, including zero. For generated keys:

- **Commit** on $(k,f)$ produces a commitment $c$ and decommitment information $d$.
- **Open** on $(k,c,f,d)$ returns $(f,d)$. **VerifyPoly** checks this full opening against $k,c$.
- **CreateWitness** on $(k,f,i,d)$ returns $(i,f(i),w_i)$. **VerifyEval** checks the claimed value and witness at $i$ against $k,c$.

Correctness requires the full opening and **every** honest evaluation opening at **every** index to verify for the same honest commitment outcome. This condition concerns which outputs can occur. It does not establish that the operations have uniform efficient implementations or that anything is hidden.

## Binding and hiding

The report uses adversaries that are probabilistic polynomial-time (PPT) in $\kappa$, except where expressly unbounded. In each binding experiment a fresh key is generated and only its public part is given to the adversary. For **every** PPT algorithm the probability of the corresponding event must be negligible in $\kappa$:

- **Polynomial binding:** it reports two accepted full openings of one commitment to *different formal polynomials*. Different decommitments alone do not count.
- **Evaluation binding:** it reports two accepted evaluations of one commitment at a *single index*, with *different field values*. Different witnesses alone do not count.

For hiding, draw $f$ uniformly from the $p^{t+1}$ bounded formal polynomials and commit honestly. The adversary sees $k,c$ and legitimately disclosed triples $(i,f(i),w_i)$ accepted by **VerifyEval**. The source describes a collection indexed up to $\deg f$, not up to the setup bound regardless of $f$. Interpret zero as having zero disclosure budget, as for constants. The number of disclosed points, their indices, values and witnesses are visible. The prediction index must be **unqueried**.

- **Computational hiding:** every PPT algorithm has negligible absolute probability of correctly predicting such a value. This is not a negligible *excess* over blind guessing. Even with no disclosures, an [independent uniform field guess](polynomial-commitment-blind-guess.md) succeeds with probability $1/p$. Hence the setup average of $1/p$ must be negligible when blind guessing is available; for example $p\ge 2^\kappa$ suffices for this baseline, but a fixed prime does not.
- **Unconditional hiding:** even an unbounded observer obtains no information about the fresh value beyond the legitimately public evaluation data. This is an information statement, not zero probability of a lucky guess. The comparison must retain the visible indices, values and count, which may themselves give information about the degree. In the [fixed pre-commitment batch formulation](polynomial-commitment-unconditional-hidi.md), adding the commitment and witnesses to that disclosed list leaves the conditional distribution of the fresh value unchanged.

## Request timing and computational scope

Definition 3.1 specifies what openings are given, not a protocol for choosing their indices. A precise experiment must specify who requests them and when. A batch selected from the public key before commitment, a batch selected **after seeing the commitment** but before any replies, and sequential requests depending on earlier replies give the requester different information. In all cases the request policy must not read the polynomial or decommitment directly. The [pre-commitment batch](polynomial-commitment-observation.md) and [post-commitment request law](polynomial-commitment-requested-trace.md) illustrate the distinction; neither asserts equivalence to an adaptive protocol. Thaler describes opening at a verifier-chosen point, not such an equivalence.

A computational instantiation must account for the uniform algorithms, encodings of parameters and messages, randomness, running times, and treatment of malformed reports. A predicate on arbitrary probability laws, even one quantified over a nonempty chosen class, need not quantify over all PPT algorithms. The [class-relative pre-commitment batch condition](polynomial-commitment-relative-batch.md) is a separate mathematical specification, not a substitute for the general definition.

## Depends on

- [Distributional interface for honest operations](polynomial-commitment-scheme.md)
- [Honest full and evaluation correctness](polynomial-commitment-honest.md)
- [Polynomial binding conflict](polynomial-binding-conflict.md)
- [Evaluation binding conflict](evaluation-binding-conflict.md)
- [The commitment and disclosed evaluations at a given public key](polynomial-commitment-view.md)
- [Correct prediction at an undisclosed index](polynomial-commitment-fresh-prediction.md)
- [Negligible advantage as a function of the security parameter](../../security-games/asymptotic-security/negligible-adv.md)
- [Polynomial-time computable functions on encoded data](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)
- [Uniform probabilistic polynomial-time adversaries](../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Sources

- A. Kate, G. M. Zaverucha and I. Goldberg, [*Polynomial Commitments*](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), CACR 2010-10, December 1, 2010, §2 (computational convention), §3.1, Definition 3.1, pp. 5–6. Conference version: *Constant-Size Commitments to Polynomials and Their Applications*, ASIACRYPT 2010.
- J. Thaler, [*Proofs, Arguments, and Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), July 18, 2023 manuscript, §7.3.1, p. 109 (degree bound and opening at a verifier-chosen point).
