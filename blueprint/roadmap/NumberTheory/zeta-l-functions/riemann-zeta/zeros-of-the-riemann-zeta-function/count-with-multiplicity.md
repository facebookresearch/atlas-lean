# Zero count with multiplicity

Sum the natural orders of vanishing of $f$ over $S$.
This counts zeros with multiplicity when $S$ is a finite set of zeros at which $f$ is analytic
and has finite order. `analyticOrderAt` returns zero at nonanalytic points, and conversion to
`ℕ` sends infinite order to zero. The finite sum is zero when its support is infinite.
