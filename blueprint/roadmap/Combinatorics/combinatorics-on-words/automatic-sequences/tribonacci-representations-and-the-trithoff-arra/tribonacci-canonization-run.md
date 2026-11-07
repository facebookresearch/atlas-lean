# Canonization run

Words are written most significant digit first. The run of at most
$n$ canonization steps on a word $w$ of natural numbers is defined by recursion on $n$: it
returns $w$ if $n = 0$ or if $w$ is canonical (every digit is $0$ or $1$ and there are no
three consecutive $1$s); otherwise it applies one canonization step to $w$ and returns the
run of at most $n - 1$ steps on the result, and it is undefined when that step is undefined.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 6.1.
