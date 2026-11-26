# Partition refinement of deterministic channels is factorization

A deterministic [channel](information-theoretic-channels.md) $C$ from $\mathcal X$ induces the partition of $\mathcal X$ given by $x_1 \sim_C x_2$ iff $C(x_1) = C(x_2)$. For
deterministic channels write $C_1 \sqsubseteq C_2$ if each equivalence class of $\sim_{C_2}$ is contained in an equivalence class of $\sim_{C_1}$, that is,
$x_1 \sim_{C_2} x_2$ implies $x_1 \sim_{C_1} x_2$ (partition refinement in the lattice of information).

**Theorem.** Let $C_1$ from $\mathcal X$ to $\mathcal Z$ and $C_2$ from $\mathcal X$ to $\mathcal Y$ be deterministic channels. Then $C_1 \sqsubseteq C_2$ if and only if there is a
deterministic channel $C_3$ from $\mathcal Y$ to $\mathcal Z$ with $C_1 = C_2 C_3$.

This is the deterministic case of [composition refinement](composition-refinement-of-channels.md).

## Depends on

- [Information-theoretic channels](information-theoretic-channels.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI, Definition 6.2 and Theorem 6.1 with its proof.
