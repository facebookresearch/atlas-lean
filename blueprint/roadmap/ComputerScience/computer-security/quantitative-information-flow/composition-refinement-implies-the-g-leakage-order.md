# Composition refinement implies the strong g-leakage order

**Theorem.** If $C_1 \sqsubseteq_\circ C_2$, then $C_1 \le_G C_2$: whenever $C_1$ is a [composition refinement](composition-refinement-of-channels.md) of $C_2$, then
$V_g(\pi, C_1) \le V_g(\pi, C_2)$ for every prior $\pi$ and every gain function $g$, so the g-leakage of $C_1$ never exceeds that of $C_2$ for every positive gain function.
This is a generalized data-processing inequality.

If $C_1 = C_2 C_3$, any guessing strategy $S$ for $C_1$ yields the strategy $C_3 S$ for $C_2$ with the same expected gain, so $V_g(\pi, C_1) \le V_g(\pi, C_2)$.

## Depends on

- [Composition refinement of channels](composition-refinement-of-channels.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI, Theorem 6.2 and its proof.
- A. McIver, C. Morgan, G. Smith, B. Espinoza and L. Meinicke, "Abstract channels and their robust information-leakage ordering", *Principles of Security and Trust (POST 2014)*, LNCS 8414, Springer, 2014, pp. 83–102, copy at <https://trustworthy.systems/publications/nicta_full_text/7522.pdf>: Section 5, Theorem 8 (a generalized data-processing inequality for g-leakage) and its proof.
