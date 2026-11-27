# Classical capacity of the generalized amplitude-damping channel

Let $0\le\gamma,\nu\le1$. On one qubit let $\Phi(P)=\sum_{r=0}^3K_rPK_r^*$ with
$K_0=\sqrt{1-\nu}\operatorname{diag}(1,\sqrt{1-\gamma})$,
$K_1=\sqrt{\gamma(1-\nu)}|0\rangle\langle1|$,
$K_2=\sqrt\nu\operatorname{diag}(\sqrt{1-\gamma},1)$ and
$K_3=\sqrt{\gamma\nu}|1\rangle\langle0|$.
The $n$-use channel is $\Phi^{\otimes n}$. Define $\chi_n$ as the supremum over all finite ensembles $(w_a,P_a)$ of density matrices on $n$ qubits of
$[S(\sum_aw_a\Phi^{\otimes n}(P_a))-\sum_aw_a S(\Phi^{\otimes n}(P_a))]/\log2$,
where $S(P)=-\operatorname{tr}(P\log P)$ with $0\log0=0$. Put $H(t)=-t\log t-(1-t)\log(1-t)$ and

$$
b(p)=H((1-\gamma)p+\gamma\nu)-H((1+\sqrt{1-4v(p)})/2),\qquad
v(p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2.
$$

For every $n\ge1$, $\chi_n=n\chi_1$. There exists a maximizer $p\in[0,1]$ of $b$ and for this $p$, $\chi_n=nb(p)/\log2$ for all $n\ge1$. For every maximizing $p$, the $2^n$ equiprobable tensor products of the phase-pair unit vectors $\sqrt{1-p}|0\rangle\pm\sqrt p|1\rangle$ give density matrices and attain $\chi_n$.

The classical capacity is $\chi_1$ bits per use. Here capacity is the supremum of rates bounded by the limit inferior of $n^{-1}\log_2 M_n$ along a sequence of codes with average error tending to zero. A code has $M_n>0$ messages, arbitrary $n$-qubit density-matrix encodings, and one collective decoding POVM. There is no preshared entanglement or feedback and no assertion of additivity with a different partner channel.

**Conventions.** Use the four Kraus operators, finite-dimensional quantum states and measurement effects, tensor powers, spectral entropy in nats, and the separate operational coding definition in bits.

## Depends on

- [Generalized amplitude-damping Kraus channel and finite codes](generalized-amplitude-damping-model.md)

## Proof depends on

A multiletter Holevo upper bound that allows entangled inputs, the one-letter scalar entropy optimization and its phase-pair witness, and coding achievability plus a collective-measurement converse linking the operational capacity to the Holevo values.

## Expansion

Identify the concrete Kraus sum with the native channel API and prove trace preservation, including parameter endpoints. Separate the scalar maximization, explicit ensemble, unrestricted repeated-use bound, and operational coding theorem; a product ensemble only gives the lower bound on the unrestricted optimum.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AmplitudeDamping.lean#L113-L123)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/276.md)
- [Accompanying manuscript: Classical capacity and entropy inequalities for generalized amplitude damping](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/paper.pdf)
- [Background: Holevo, The capacity of the quantum channel with general signal states](https://arxiv.org/abs/quant-ph/9611023)
- [Background: Schumacher and Westmoreland, Sending classical information via noisy quantum channels](https://doi.org/10.1103/PhysRevA.56.131)
- [Background: Khatri, Sharma and Wilde, Information-theoretic aspects of the generalized amplitude-damping channel](https://arxiv.org/abs/1903.07747)
