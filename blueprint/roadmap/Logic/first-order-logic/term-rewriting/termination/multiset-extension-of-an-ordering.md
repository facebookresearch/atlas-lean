# Multiset extension of an ordering

A (finite) *multiset* over a set $M$ is a map $S : M \to \mathbb{N}$ that is nonzero at finitely many elements; $m \in S$ means $S(m) > 0$, $(S_1 \cup S_2)(m) = S_1(m) + S_2(m)$, $(S_1 - S_2)(m) = \max(S_1(m) - S_2(m), 0)$, and $S_1 \subseteq S_2$ means $S_1(m) \le S_2(m)$ for all $m$. Now let $M$ be nonempty and $\succ$ a binary relation on $M$, so that $(M, \succ)$ is an [abstract reduction system](../abstract-reduction-system.md). Its *multiset extension* $\succ_{\mathrm{mul}}$ relates finite multisets over $M$ by $S_1 \succ_{\mathrm{mul}} S_2$ if there are multisets $X$ and $Y$ with

$$\emptyset \ne X \subseteq S_1, \qquad S_2 = (S_1 - X) \cup Y, \qquad \forall y \in Y\ \exists x \in X:\ x \succ y.$$

So $S_2$ arises from $S_1$ by replacing a nonempty part by elements each smaller than some removed element. For example, over $(\mathbb{N}, >)$, $\{5, 3, 1, 1\} \succ_{\mathrm{mul}} \{4, 3, 3, 1\}$, replacing $5$ and one $1$ by $4$ and $3$.

## Depends on

- [Abstract reduction system](../abstract-reduction-system.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.4, multisets over a set (p. 8) and the multiset extension for an abstract reduction system $(M, \succ)$ (p. 9), with Section 1.2, p. 3, for abstract reduction systems on a nonempty set; the extension is due to N. Dershowitz and Z. Manna (1979).
