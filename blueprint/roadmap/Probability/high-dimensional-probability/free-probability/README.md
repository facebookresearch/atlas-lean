# Free probability

Free probability is noncommutative probability with *free independence* in place of independence.
A noncommutative probability space is a unital complex algebra $A$ with a linear functional
$\varphi$ such that $\varphi(1) = 1$; unital subalgebras $(A_j)$ are free when every alternating
product of centred elements is centred. Free independence describes large random matrices: Voiculescu
showed that independent Wigner matrices, or $A_N$ and $U_N B_N U_N^*$ with $U_N$ Haar unitary, are
asymptotically free, so the spectrum of a sum is given by the free additive convolution of the
spectra.

The combinatorics is that of noncrossing partitions. Free cumulants $\kappa_n$ are defined by the
moment-cumulant formula $m_n = \sum_{\pi \in NC(n)} \prod_{V \in \pi} \kappa_{|V|}$; they are
additive for free variables, so the R-transform $R(z) = \sum_n \kappa_{n+1} z^n$ linearises free
convolution, as the logarithm of the Fourier transform linearises classical convolution. The
semicircle law plays the role of the Gaussian: its only nonzero free cumulant is $\kappa_2$, its
R-transform is $z$, and it is the limit in the free central limit theorem.

Families with at most one member, and families in which all but one member is the algebra of scalars, are free
for trivial reasons. Non-trivial free families include the group algebra of a free group with its canonical trace
and free semicircular families on the full Fock space.

- [Free independence](is-freely-independent.md)
- [Free random variables](are-free.md)
- [A family with at most one member is free](of-subsingleton.md)
- [Scalars are free from everything](is-freely-independent-of-eq-bot.md)
- [Free variables are uncorrelated](map-mul.md)
- [Free cumulants of a moment sequence](free-cumulant.md)
- [Moment-cumulant formula](moment-eq-sum-noncrossing-prod-free-cumu.md)
- [The first free cumulant is the mean](free-cumulant-one.md)
- [The second free cumulant is the variance](free-cumulant-two.md)
- [The R-transform](r-transform.md)
- [Moments of the semicircle law](semicircle-moment.md)
- [The free cumulants of the semicircle law](free-cumulant-semicircle.md)
- [The R-transform of the semicircle law is $z$](r-transform-semicircle.md)
- [Free cumulants are additive for free variables](free-cumulant-add-of-are-free.md)
- [The free central limit theorem](free-central-limit.md)

## Related topics

- [Wigner's semicircle law](../wigner-s-semicircle-law/README.md)
- [Noncrossing pair partitions and the Catalan count](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-pair-partitions-and-the-catalan-count/README.md)
- [Noncrossing partitions and the refinement order](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-partitions-and-the-refinement-order/README.md)
- [Ben Arous–Guionnet large deviations](../../large-deviations/ben-arous-guionnet-large-deviations/README.md)
