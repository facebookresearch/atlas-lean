# The closed form is the satisfaction probability

Let $C$ be a clause whose literals $\ell_1, \dots, \ell_k$ use distinct variables $V$, and let $p_i \in [0, 1]$ for every variable $i$. Then

$$1 - \prod_{j} \bigl(1 - P[\ell_j]\bigr) = \sum_{a : V \to \{\mathrm{true}, \mathrm{false}\}} \Bigl(\prod_{i \in V} \pi_i(a_i)\Bigr) \cdot [a \text{ satisfies } C],$$

with $\pi_i(\mathrm{true}) = p_i$ and $\pi_i(\mathrm{false}) = 1 - p_i$, and $P[\ell] = p_i$ or $1 - p_i$ for a positive or negative literal on $i$. That is, the closed form is the probability that $C$ is satisfied when each variable is set true independently with probability $p_i$ (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2): because the literals use distinct variables, exactly one assignment falsifies $C$, the one making every literal false, with probability $\prod_j (1 - P[\ell_j])$.
