# Rows of the centred leaf covariance sum to zero

Let `μ` be a measure and let the allele frequencies `p X` of a finite set of populations be square
integrable with respect to `μ`. Then every row of the [centred leaf covariance](centred-cov.md) sums
to zero: `∑ Y, K(X, Y) = 0` for every population `X`. Indeed the row sum is the integral of
`(p X - p̄) * ∑ Y, (p Y - p̄)`, and at each outcome the frequencies centred across populations sum
to zero, `∑ Y, (p Y - p̄) = 0`, where `p̄` is the [mean frequency across populations](pop-mean.md).
