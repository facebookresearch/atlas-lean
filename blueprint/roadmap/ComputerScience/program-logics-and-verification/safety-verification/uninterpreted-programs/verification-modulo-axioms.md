# Verification of uninterpreted programs modulo axioms

Verification modulo axioms restricts the data models of an uninterpreted program to those satisfying a set of first-order axioms, such as associativity of a function or transitivity of a relation. Coherence modulo axioms extends the memoizing and early-assume conditions with equivalence of terms modulo the axioms.

**Setting (Mathur, Madhusudan and Viswanathan).** Programs are [uninterpreted programs](uninterpreted-programs-and-their-verification.md) over variables $V$ and a signature of constants, functions and relation symbols, whose conditions may also be relational atoms $R(\vec{z})$ and their negations. For an execution $\rho$, $\mathrm{comp}(\rho, x)$ is the term stored in $x$ and $\kappa(\rho)$ the set of ground equalities, disequalities and relational literals over computed terms assumed along $\rho$. Let $\mathcal{A}$ be a set of first-order sentences. A data model is an $\mathcal{A}$-model if it satisfies every sentence of $\mathcal{A}$, and $\rho$ is *feasible modulo $\mathcal{A}$* if it is feasible in some $\mathcal{A}$-model. A program $s$ satisfies a postcondition $\varphi$ built from $x = y$ and $R(\vec{z})$ by $\vee$ and $\neg$ *modulo $\mathcal{A}$* if, for every $\mathcal{A}$-model $\mathcal{M}$ and every complete execution of $s$ feasible in $\mathcal{M}$, $\mathcal{M}$ satisfies $\varphi$ at the end of the execution.

**Definition (coherence modulo axioms).** Write $t \cong_\Gamma t'$ when $\Gamma \models t = t'$. An execution $\rho$ is *coherent modulo $\mathcal{A}$* if:

- (memoizing) for every prefix $\pi = \sigma \cdot (x := f(\vec{z}))$ with $t = \mathrm{comp}(\pi, x)$, if $t \cong_{\mathcal{A} \cup \kappa(\sigma)} t'$ for some term $t'$ computed in $\sigma$, then $t \cong_{\mathcal{A} \cup \kappa(\sigma)} \mathrm{comp}(\sigma, y)$ for some $y \in V$;
- (early assumes) for every prefix $\pi = \sigma \cdot \mathtt{assume}(c)$ and every term $t$ computed in $\sigma$ that has been dropped (no variable holds a term $\cong_{\mathcal{A} \cup \kappa(\sigma)} t$), if $t \cong_{\mathcal{A} \cup \kappa(\pi)} t'$ for a term $t'$ computed in $\sigma$, then already $t \cong_{\mathcal{A} \cup \kappa(\sigma)} t'$.

A program is coherent modulo $\mathcal{A}$ if all its executions are. *Coherent verification modulo $\mathcal{A}$* asks, for a program coherent modulo $\mathcal{A}$ and a postcondition, whether the program satisfies it modulo $\mathcal{A}$.

## Depends on

- [Uninterpreted programs and their verification problem](uninterpreted-programs-and-their-verification.md)

## Proof depends on

None.

## Expansion

With $\mathcal{A} = \emptyset$ every execution coherent in the earlier sense is coherent modulo $\emptyset$, but not conversely: here all assumes, not only equality assumes, must be early. Coherent verification stays decidable modulo several axiom classes, such as relations required to be reflexive, symmetric, transitive, partial or total orders, and functions required to be commutative or idempotent.

## Sources

- Umang Mathur, P. Madhusudan and Mahesh Viswanathan, "What's Decidable About Program Verification Modulo Axioms?", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), Part II, Lecture Notes in Computer Science 12079, pp. 158–177, Springer, 2020, <https://doi.org/10.1007/978-3-030-45237-7_10>; the subsections on feasibility and program verification modulo axioms in Section 3 and the definition of coherence modulo axioms in Section 4 of arXiv:1910.10889v2 (the copy read), <https://arxiv.org/abs/1910.10889v2>.
