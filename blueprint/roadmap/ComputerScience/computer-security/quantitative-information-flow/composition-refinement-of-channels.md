# Composition refinement of channels

Let $C_1$ be a [channel](information-theoretic-channels.md) from $\mathcal X$ to $\mathcal Z$ and $C_2$ a channel from $\mathcal X$ to $\mathcal Y$. $C_1$ is *composition refined*
by $C_2$, written $C_1 \sqsubseteq_\circ C_2$, if there is a channel $C_3$ from $\mathcal Y$ to $\mathcal Z$ with $C_1 = C_2 C_3$: $C_1$ can be obtained by post-processing the
output of $C_2$.

For a set $\mathcal G$ of gain functions write $C_1 \le_{\mathcal G} C_2$ if $V_g(\pi, C_1) \le V_g(\pi, C_2)$ for every prior $\pi$ and every $g \in \mathcal G$, which for a
positive gain function $g$ is equivalent to $L_g(\pi, C_1) \le L_g(\pi, C_2)$ for every prior, in terms of the [g-leakages](g-leakage-and-g-capacity.md); $\le_G$ denotes this order for the set $G$ of all
gain functions, the *strong g-leakage order*.

## Depends on

- [Information-theoretic channels](information-theoretic-channels.md)
- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI, Definitions 6.1 and 6.3 and the notation $\le_g$, $\le_{\mathcal S}$ and $\le_G$.
- A. McIver, C. Morgan, G. Smith, B. Espinoza and L. Meinicke, "Abstract channels and their robust information-leakage ordering", *Principles of Security and Trust (POST 2014)*, LNCS 8414, Springer, 2014, pp. 83–102, copy at <https://trustworthy.systems/publications/nicta_full_text/7522.pdf>: Section 2 (gain functions and g-leakage) and Section 4, Definition 4 (composition refinement).
