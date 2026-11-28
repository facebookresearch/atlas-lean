# Natarajan's cardinality bound for multiclass classes on finite domains

Let $X$ be a finite set, $\beta$ a finite set of $k \ge 1$ labels and $C$ a set of functions $X \to \beta$ with Natarajan dimension $d$. Then

$$
|C| \le |X|^{d}\, k^{2d}.
$$

For $k = 2$ this recovers the corresponding consequence of Sauer's lemma for binary classes.

## Proof sketch

Apply Natarajan's lemma to the set $C$ itself, viewed as labelings of the $n = |X|$ points of the domain, and bound the sum by $n^d k^{2d}$ (for $n \ge 1$; the case of an empty domain is trivial since then $|C| \le 1$).

## Depends on

- [Natarajan dimension at most d](../natarajan-dimension-and-the-natarajan-lemma/ndim-le.md)
- [Natarajan's lemma](natarajans-lemma.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
