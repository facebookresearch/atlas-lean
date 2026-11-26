# Conditional entropy is at most the expected length of a fiberwise prefix-free transcript

Let $\nu$ be a distribution on a finite set $\Omega$ and let $\mathrm{obs} : \Omega \to O$, $\mathrm{tgt} : \Omega \to Z$ and $\mathrm{msg} : \Omega \to \{0,1\}^*$ be maps. Suppose that for every observation $o$, the messages $\{\mathrm{msg}(\omega) : \omega \in \mathrm{supp}\,\nu,\ \mathrm{obs}(\omega) = o\}$ form a prefix-free set, and that $\mathrm{msg}(\omega)$ together with $\mathrm{obs}(\omega)$ determines $\mathrm{tgt}(\omega)$ on $\mathrm{supp}\,\nu$. Then

$$
H\big(\mathrm{tgt}(\omega) \,\big|\, \mathrm{obs}(\omega)\big) \le \mathbb{E}_{\omega \sim \nu}\big[\,|\mathrm{msg}(\omega)|\,\big],
$$

with entropy in bits. The special case of a trivial observation is $H(p) \le \mathbb{E}_{x\sim p}|\mathrm{enc}(x)|$ for any encoding $\mathrm{enc}$ that is injective with prefix-free image on $\mathrm{supp}\,p$; no positivity of $p$ is required.

## Proof sketch

For a fixed observation, Kraft's inequality gives $\sum 2^{-|\mathrm{msg}|} \le 1$ over the fiber, so $2^{-|\mathrm{msg}|}$ is a sub-probability weight on target values; Gibbs' inequality bounds the fiber's conditional entropy by its expected message length. Averaging over observations gives the claim.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Prefix-free code](../prefix-codes/is-prefix-free.md)
- [Shannon source coding lower bound](../shannon-s-source-coding-theorem/shannon-source-coding-lower-bound.md)

## Proof depends on

- [Kraft's inequality for prefix codes](../kraft-mcmillan-lengths.md)
- [Gibbs' inequality](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
- L. G. Kraft, "A Device for Quantizing, Grouping, and Coding Amplitude-Modulated Pulses", M.S. thesis, Massachusetts Institute of Technology, 1949.
