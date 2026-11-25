# TDT with a random number of informative transmissions

Let $\mu$ be a probability measure, $D$ a measurable natural-valued random variable, the number of
informative transmissions (from heterozygous parents), and $B$ a natural-valued random variable, the
number of those transmissions that pass on the allele of interest. Suppose that for every $d$ with
$\mu(D = d) > 0$, the count $B$ has the law $\mathrm{Bin}(d, 1/2)$ under $\mu$ conditioned on the
event $\{D = d\}$ (the null of no linkage, with the transmissions treated as independent fair coins
given $d$). Then the [TDT p-value](tdt-pvalue.md) at the observed total,
$P(\omega) = \Pr[\mathrm{Bin}(D(\omega), 1/2) \ge B(\omega)]$, is
[valid](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under $\mu$: $\mu(P \le t) \le t$ for every $t \in [0, 1]$. It follows by averaging the
[validity for a fixed number of transmissions](is-valid-pvalue-tdt-pvalue.md) over the values of
$D$.
