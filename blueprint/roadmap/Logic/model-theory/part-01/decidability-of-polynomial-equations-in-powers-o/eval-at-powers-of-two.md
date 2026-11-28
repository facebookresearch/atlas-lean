# Evaluating an integer polynomial at powers of two

For an encoded integer polynomial $P$, given as a list of monomials $(c, (e_0, \dots, e_k))$, and a sequence $n : \mathbb{N} \to \mathbb{N}$, the value of $P$ at $(2^{n_0}, 2^{n_1}, \dots)$ is the integer

$$P(2^{n_0}, 2^{n_1}, \dots) = \sum_{(c, (e_0, \dots, e_k)) \in P} c \prod_{j=0}^{k} \left(2^{n_j}\right)^{e_j},$$

with the sum taken over the list (with repetitions), so the empty list gives $0$.
