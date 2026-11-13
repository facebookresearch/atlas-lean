# Residue counts of the shifted floor sequence

For a natural number $n$, real numbers
$\alpha$ and $\nu$, an integer $r$ and a natural number $m$, the count
$\mathcal N_{n,\alpha,\nu,r,m}$ is the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. In other words, it counts the terms of
the $\alpha$-shifted, $\nu$-offset floor sequence
$\lfloor (n - \nu)/1 + \alpha \rfloor, \dots, \lfloor (n - \nu)/n + \alpha \rfloor$ that are
congruent to $r$ modulo $m$, where congruence modulo $0$ means equality.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Section 4 (definition of `𝓝_{n,α,ν,r,m}`).
