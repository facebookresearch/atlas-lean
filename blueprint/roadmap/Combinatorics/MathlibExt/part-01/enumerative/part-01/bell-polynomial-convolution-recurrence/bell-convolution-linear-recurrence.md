---
article_id: af_ec9b16ded0b5d6dec1b90825
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bell_convolution_linear_recurrence
---

# Bell convolution linear recurrence

Linear recurrence for the `r`-fold convolution of the INVERT transform sequence
`y` built from partial exponential Bell polynomials in the coefficients `c`.
The hypothesis `hBell` expands `y n` as the Bell sum over `k = 0..n`, and
`conv` is the `r`-fold convolution over compositions of `N`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bell convolution linear recurrence of char Zero](bell-convolution-linear-recurrence-of-ch.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BellPolynomialConvolutionRecurrence](../../../../../../../sources/v2/MathlibExt.md)
- Daniel Birmajer, Juan B. Gil, and Michael D. Weiner, "Linear Recurrence Sequences and Their Convolutions via Bell Polynomials," Journal of Integer Sequences 18 (2015), Article 15.1.2, Theorem (label `thm:linearRecurrence`), equation (label `eq:linearRecurrence`), lines 425–435, https://cs.uwaterloo.ca/journals/JIS/VOL18/Gil/gil3.tex
