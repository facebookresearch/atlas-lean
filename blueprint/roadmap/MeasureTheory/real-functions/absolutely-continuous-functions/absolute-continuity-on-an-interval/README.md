# Absolute continuity on an interval

Let $X$ be a pseudometric space, such as $\mathbb{C}$, let $f \colon \mathbb{R} \to X$, and let $a, b \in \mathbb{R}$,
with $I$ the closed interval with endpoints $a$ and $b$. Then $f$ is absolutely continuous on $I$ if for every
$\varepsilon > 0$ there is $\delta > 0$ such that $\sum_{i < n} d(f(a_i), f(b_i)) < \varepsilon$ for every finite family
of pairs $(a_i, b_i)$ of points of $I$ whose intervals $(\min(a_i, b_i), \max(a_i, b_i)]$ are pairwise disjoint and
whose total length $\sum_{i < n} |a_i - b_i|$ is less than $\delta$; equivalently, these sums tend to $0$ as the total
length tends to $0$. This is the general form of absolute continuity of a function $F \colon [a, b] \to \mathbb{C}$ with
$a < b$: extending $F$ to $\mathbb{R}$ in any way and taking $X = \mathbb{C}$ gives the textbook definition, which uses
disjoint open intervals $(a_i, b_i)$ with $a_i < b_i$, a change that alters neither the sums nor the disjointness of
nondegenerate intervals.

## Idea

Absolute continuity strengthens uniform continuity by allowing many small intervals at once. Lipschitz functions are
absolutely continuous, and absolutely continuous functions have bounded variation. By the fundamental theorem of
calculus for the Lebesgue integral, the real or complex absolutely continuous functions on $[a, b]$ are exactly the
indefinite integrals $F(x) = F(a) + \int_a^x g$ of integrable functions $g$. The Cantor function is continuous and
increasing but not absolutely continuous: its derivative is $0$ almost everywhere, yet it is not constant.

## Statements

- [Absolutely continuous function on an interval](absolutely-continuous-on-interval.md)
