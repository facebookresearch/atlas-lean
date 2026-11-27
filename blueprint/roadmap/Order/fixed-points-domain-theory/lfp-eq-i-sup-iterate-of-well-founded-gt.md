# Kleene iteration reaches the least fixed point under the ascending chain condition

Let $A$ be a complete lattice with no infinite strictly ascending chain $a_0 < a_1 < a_2 < \cdots$, for example a lattice of finite height, or the order dual of $\mathbb{N} \cup \{\infty\}$, which has chains of every finite length. Let $f : A \to A$ be monotone, and write $f^n$ for the $n$-fold iterate of $f$, with $f^0$ the identity. Then the least fixed point of $f$ is the supremum of its iterates from the least element,

$$\operatorname{lfp} f = \bigsqcup_{n \ge 0} f^n(\bot),$$

and it is one of them: $f^k(\bot) = \operatorname{lfp} f$ for some $k \in \mathbb{N}$.

## Proof sketch

Every iterate lies below $\operatorname{lfp} f$, by induction, since $f$ is monotone and fixes $\operatorname{lfp} f$. By monotonicity the chain $\bot \le f(\bot) \le f^2(\bot) \le \cdots$ is increasing, so it is eventually constant, at some $f^k(\bot)$. Then $f(f^k(\bot)) \le f^k(\bot)$, and the least fixed point lies below every such element, so $f^k(\bot) = \operatorname{lfp} f$, which is therefore the supremum of the chain.

## Remarks

No continuity of $f$ is assumed. For Scott-continuous maps, the supremum of the iterates is the least fixed point without the chain condition ([Kleene's fixed-point theorem for pointed dcpos](scott-continuous-maps-and-least-fixed-points/map-i-sup-iterate-bot.md), [Kleene's fixed point is the least prefixed point](scott-continuous-maps-and-least-fixed-points/i-sup-iterate-bot-le.md)). On a finite partial order with a least element, [Kleene iteration from the bottom stabilizes](../../ComputerScience/programming-language-semantics/dataflow-analysis-by-kleene-iteration/kildall-stabilizes.md) without a lattice structure.

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>, Section 4.4, pp. 47–48 (the fixed-point theorem for lattices of finite height, attributed there to Kleene, and its proof)
