# Peak generating function for set partitions

Let $k \ge 1$. Work in the fraction field of
the ring $\mathbb{Z}[q][[x]]$ of power series in $x$ with coefficients in $\mathbb{Z}[q]$. For
a word $w = w_0 \cdots w_{n-1}$, let $\mathrm{pk}(w)$ be the number of positions $a$ with
$a + 2 < n$ and $w_a < w_{a+1} > w_{a+2}$, and let $W_{n,k}$ be the set of surjective
restricted-growth strings of length $n$ with letters in $\{0, \dots, k-1\}$. Let
$t = 1 + x^2 (1-q)/2$, let $U_m = U_m(t)$ for $m \in \mathbb{Z}$, where $U_m$ is the Chebyshev
polynomial of the second kind extended to negative indices by its recurrence (so $U_{-1} = 0$
and $U_{-2} = -1$), and let $R_j = (U_j - U_{j-1})/(U_{j-1} - U_{j-2})$. Then

$$\sum_{n \ge 0} \sum_{w \in W_{n,k}} q^{\mathrm{pk}(w)} x^n = x^k (1-q)^k \prod_{j=1}^{k}
\frac{1 + x + x^2 (1-q) - R_j}{1 + x (1-q) - R_j}.$$

Set partitions of $\{1, \dots, n\}$ with $k$ blocks are encoded by the strings in $W_{n,k}$, and
$\mathrm{pk}(w)$ counts the peaks of the encoded partition. Division is total in the fraction
field, so the statement carries no nonvanishing hypotheses.

Proof: Following Mansour and Shattuck, Lemmas 2.1, 2.2, and 2.6 and Theorem 2.7,
the proof combines first-occurrence decompositions with the Chebyshev recurrence.

## Sources

- Toufik Mansour and Mark Shattuck, "Counting Peaks and Valleys in a Partition of a Set," Journal of Integer Sequences 13 (2010), Article 10.6.8, Theorem, lines 313–317, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Shattuck/shattuck3.tex>.
