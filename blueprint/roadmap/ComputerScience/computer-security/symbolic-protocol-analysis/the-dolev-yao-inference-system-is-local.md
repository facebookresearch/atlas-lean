# The Dolev–Yao inference system is local

**Proposition.** The [Dolev–Yao inference system](dolev-yao-terms-and-deduction.md) $\mathcal I_{\mathrm{DY}}$ is local: whenever $S \vdash t$, every minimal proof tree of
$S \vdash t$ has all its labels in $\mathrm{st}(S \cup \{t\})$, and in $\mathrm{st}(S)$ if it is a leaf or ends with a decomposition rule.

The proof is by induction on the size of a minimal proof: a decomposition is never applied to the result of the matching composition, since that would give a
smaller proof.

## Depends on

- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.3, Proposition 3.2 and its proof.
