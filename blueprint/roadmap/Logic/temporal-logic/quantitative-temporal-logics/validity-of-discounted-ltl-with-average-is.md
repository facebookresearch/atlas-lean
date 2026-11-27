# Validity of discounted LTL with the average operator is undecidable

Adding the average operator $\varphi \oplus \psi$ to discounted LTL makes threshold validity undecidable, for every nonempty set of discounting functions, whereas discounted LTL without averaging has decidable threshold problems.

**Theorem (Almagor, Boker and Kupferman).** For every nonempty set $\mathcal{D}$ of discounting functions, the validity problem for [$\mathrm{LTL}^{\mathrm{disc}\oplus}[\mathcal{D}]$](discounted-ltl.md) is undecidable: no algorithm decides, given a formula $\varphi$ and a threshold $v \in [0,1]$, whether $[\![\pi, \varphi]\!] > v$ for every computation $\pi$.

Undecidability already holds with a single discounting function, so it is the combination of one discounting operator with averaging that causes it.

## Depends on

- [Discounted LTL](discounted-ltl.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the $0$-halting problem for two-counter machines, which is undecidable, to the $\tfrac12$-co-validity problem: whether some computation $\pi$ has $[\![\pi, \varphi]\!] \geq \tfrac12$. A computation encodes a run as a sequence of configurations with counter values written in unary. Discounting turns the length of a block into a value, and averaging two discounted values compares them: $(\varphi_A \oplus \neg\varphi_B) \wedge (\neg\varphi_A \oplus \varphi_B)$ has value at least $\tfrac12$ exactly when the two discounted counts agree. This lets the formula check that successive configurations follow the machine's instructions. The co-validity problem is then reduced to the complement of validity.

## Sources

- S. Almagor, U. Boker and O. Kupferman, "Discounting in LTL", in *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2014)*, Lecture Notes in Computer Science 8413, Springer, 2014, pp. 424–439, doi:10.1007/978-3-642-54862-8_37; read as arXiv:1406.4249v2, <https://arxiv.org/abs/1406.4249v2>: Theorem 5 of arXiv:1406.4249v2 (the theorem in the subsection "Adding the Average Operator") and its proof.
