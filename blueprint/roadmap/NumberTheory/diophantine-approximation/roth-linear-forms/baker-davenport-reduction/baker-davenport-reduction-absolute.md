# Baker–Davenport reduction lemma, absolute-value form

For a real number $x$ write
$\lVert x \rVert = |x - \operatorname{round}(x)|$ for the distance from $x$ to a nearest integer.
Let $M$ be a positive integer and $\kappa$ an irrational real number, and let $q$ be the
denominator of the $j$-th convergent of the continued fraction of $\kappa$ for some natural number
$j$, with $q > 6M$. Let $A$, $B$, $\mu$ be real numbers with $A > 0$ and $B > 1$. Put
$\varepsilon = \lVert \mu q \rVert - M \lVert \kappa q \rVert$ and suppose that $\varepsilon > 0$.
Then there are no positive integers $r$, $s$, $w$ with $r \le M$,
$w \ge \log(Aq/\varepsilon) / \log B$ and $0 < |r\kappa - s + \mu| < A B^{-w}$.

Of the hypothesis $q > 6M$ only $q > 0$ is used. The hypotheses that $M > 0$, that $\kappa$ is
irrational and that $q$ is a convergent denominator, and the positivity of $r$, $s$, $w$ and of
$|r\kappa - s + \mu|$, are not needed: the statement follows from the version for an arbitrary
positive denominator.

Concept `baker_davenport_reduction_absolute`, semantic id
`jis_grounded_3d649f47290c78b9a73677c9`.

## Sources

- Eric F. Bravo, Carlos A. Gomez, and Florian Luca, "Product of Consecutive Tribonacci Numbers With Only One Distinct Digit," Journal of Integer Sequences 22 (2019), Article 19.6.3, Lemma `bd`, lines 285–292. Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL22/Gomez/gomez3.tex`. Source-file SHA-256 `06ab2807874c97cf44007c561d48576611214b0fa0ab6ed55c61470d8ba7c0e6`; exact-span SHA-256 `cc488ea946e7229300ad0b1a00befe1e523c8a5b97331a1d79e04c8f40429fe4`.
