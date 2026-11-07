# Letter frequencies of a substitution image

Let $\mu$ be a substitution sending the
letters $a$ and $b$ to nonempty finite words, extended to words by concatenation, such that both
$a$ and $b$ occur in $\mu(a)\mu(b)$. For a word $x$ and a letter $\alpha$ write $\#_\alpha(x, m)$
for the number of letters $\alpha$ among the first $m$ letters of $x$; for a finite word $u$
write $|u|$ for its length and $|u|_\alpha$ for the number of letters $\alpha$ in it. Let $w$ be
an infinite binary word in which both letters occur infinitely often, let $v = \mu(w)$, suppose
that $\#_a(w, m)/m \to f$ for a real number $f$, and let $L = |\mu(a)|\,f + |\mu(b)|\,(1 - f)$.
Then

$$\frac{\#_a(v, m)}{m} \to \frac{|\mu(a)|_a\,f + |\mu(b)|_a\,(1 - f)}{L}, \qquad
\frac{\#_b(v, m)}{m} \to \frac{|\mu(a)|_b\,f + |\mu(b)|_b\,(1 - f)}{L}.$$

The paper allows erasing substitutions, but then the formula fails: for $\mu(a)$ empty,
$\mu(b) = ab$ and $w$ with $b$ exactly at the perfect squares, the frequency of $a$ in $w$ is $1$
and $\mu(w) = (ab)^\omega$ has frequency of $a$ equal to $1/2$, while $L = 0$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 35 (`jis-2025-25.1.5-thm-35`).
