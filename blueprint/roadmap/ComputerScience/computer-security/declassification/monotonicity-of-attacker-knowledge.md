# Monotonicity of attacker knowledge

**Proposition.** For a command $c$, a low projection $M^0_L$ and $\vec\ell_n = \ell_1, \dots, \ell_n \in L(c, M^0_L)$, writing $\vec\ell_i$ for the prefix of length $i$,

$$k_\downarrow(c, M^0_L, \vec\ell_{i-1}) \supseteq k_\downarrow(c, M^0_L, \vec\ell_i) \qquad (1 \le i \le n),$$

where $k_\downarrow$ is the termination-insensitive [attacker knowledge](attacker-knowledge.md). Each new low event can only refine what the attacker knows about the
initial memory; it never forgets.

## Depends on

- [Attacker knowledge for programs with low events](attacker-knowledge.md)

## Sources

- A. Askarov and A. Sabelfeld, "Gradual release: unifying declassification, encryption and key release policies", *Proceedings of the 2007 IEEE Symposium on Security and Privacy*, copy at <https://www.cs.cornell.edu/~aslan/askarov-sabelfeld-sp07.pdf>: Section 2, Proposition 1 (monotonicity of knowledge).
