# A $1$-periodic entire function bounded by $C e^{|\operatorname{Im} s|}$ is constant

Let $f : \mathbb{C} \to \mathbb{C}$ be entire with $f(s + 1) = f(s)$ for all $s \in \mathbb{C}$,
and suppose there is a real constant $C$ such that $|f(s)| \le C e^{|\operatorname{Im} s|}$ for
every $s$ with $0 \le \operatorname{Re} s \le 1$. Then $f$ is constant.

The two-sided bound cannot be weakened to the one-sided $|f(s)| = O(e^{\operatorname{Im} s})$ as
$\operatorname{Im} s \to \infty$: the function $f(s) = e^{2 \pi i s}$ is entire and $1$-periodic,
satisfies $|f(s)| = e^{-2 \pi \operatorname{Im} s} \le e^{\operatorname{Im} s}$ for
$\operatorname{Im} s \ge 0$, and is not constant.

## Sources

- ATLAS `NumberTheoryI`, Lemma 17.14, corrected; the book prints the one-sided bound, under which the lemma is false.
