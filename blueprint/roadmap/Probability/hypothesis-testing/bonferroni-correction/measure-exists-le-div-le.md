# Bonferroni inequality

Let $\mu$ be a measure on $\Omega$, $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ and $H_0 \subseteq \{0, \dots, m-1\}$ such that each $p_i$, $i \in H_0$, is a valid p-value under $\mu$ ($\mu(p_i \le t) \le t$ for all $t \in [0,1]$). For every $\alpha \in [0,1]$,

$$\mu(\exists i \in H_0 : p_i \le \alpha/m) \le \frac{\alpha\,|H_0|}{m}.$$

No independence is assumed. For $m = 0$ there is no hypothesis and both sides are $0$.

## Sources

- C. E. Bonferroni, *Teoria statistica delle classi e calcolo delle probabilità*, Pubblicazioni del R. Istituto Superiore di Scienze Economiche e Commerciali di Firenze 8 (1936), 3–62.
- O. J. Dunn, *Multiple comparisons among means*, J. Amer. Statist. Assoc. 56 (1961), 52–64.
