# Level-decomposable lunar numbers

Let $b$ and $n$ be natural numbers and
$a = \lfloor b/2 \rfloor$. For a lunar number $f$ of base $b$ and degree at most $n$, given by its
digits $f_0, \dots, f_n \in \{0, \dots, b - 1\}$, write $|f_a|$ for the number of indices $k \le n$
with $f_k \ge a$. The set $\mathcal{D}_b^n$ consists of the lunar numbers $h$ of base $b$ and
degree at most $n$ such that $h = f \otimes g$ for some lunar numbers $f$ and $g$ of base $b$ and
degree at most $n$ with $|f_a| \ge 2$ and $|g_a| \ge 2$, where $\otimes$ is the max-min product of
coefficient sequences.

For $b \ge 2$ we have $a \ge 1$, so $|f_a| \ge 2$ implies that $f$ has at least two nonzero
digits; hence $\mathcal{D}_b^n$ is contained in the set $\Sigma_b^n$ of decomposable lunar numbers
of degree at most $n$, and one writes $\mathcal{I}_b^n = \Sigma_b^n \setminus \mathcal{D}_b^n$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2, before Remark 22.
