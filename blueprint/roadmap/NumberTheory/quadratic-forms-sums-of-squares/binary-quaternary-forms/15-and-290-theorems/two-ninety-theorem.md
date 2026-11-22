# The 290 theorem

Let $n$ be a natural number and let $M$ be a real $n \times n$ matrix
that is positive definite (symmetric, with $x^{\top} M x > 0$ for every nonzero
$x \in \mathbb{R}^n$) and integral (for every $x \in \mathbb{Z}^n$, the value $x^{\top} M x$ is
an integer). If $M$ represents each of the 29 critical numbers of the 290 theorem, that is,
for each critical number $m$ there is $x \in \mathbb{Z}^n$ with $x^{\top} M x = m$, then $M$
is universal: for every positive integer $m$ there is $x \in \mathbb{Z}^n$ with
$x^{\top} M x = m$.

## Sources

- M. Bhargava, J. Hanke, Universal quadratic forms and the 290-theorem, preprint (2011). See also https://en.wikipedia.org/wiki/15_and_290_theorems. Problem `two_ninety_theorem` of the lean-eval benchmark.
