# Events and correspondence properties

Extend the plain processes of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md) with *events* $\mathbf{event}\ e(t).P$, where $e$ is drawn from a set of event symbols outside the signature and
$t$ is a term, and add the reduction $\mathbf{event}\ e(t).P \to P$ to [internal reduction](internal-reduction-in-the-applied-pi-calculus.md). A reduction sequence
$R = A_0 \xrightarrow{\alpha_1} A_1 \cdots \xrightarrow{\alpha_n} A_n$ *satisfies $e(t)$ at step $i$* if $A_{i-1} \equiv C[\mathbf{event}\ e(t).P]$ and $A_i \equiv C[P]$ for some context $C$ and process $P$.

A closed extended process $A$ satisfies the *correspondence property* $e(t) \rightsquigarrow e'(t')$ if every reduction sequence of $A$ that satisfies $e(t\sigma)$ also satisfies $e'(t'\sigma)$, for every
substitution $\sigma$ with domain $\mathrm{fv}(t, t')$; it satisfies the *injective* correspondence $e(t) \rightsquigarrow_{\mathrm{inj}} e'(t')$ if for every reduction sequence there is a partial injective map
$\varphi$ on steps such that each step $i$ satisfying $e(t\sigma)$ has $e'(t'\sigma)$ satisfied at step $\varphi(i)$.

## Depends on

- [Internal reduction in the applied pi calculus](internal-reduction-in-the-applied-pi-calculus.md)
- [Labelled transitions in the applied pi calculus](labelled-transitions-in-the-applied-pi-calculus.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 6.1 (events, Definition 6.1) and Section 6.3.1 (Definitions 6.3 and 6.4).
