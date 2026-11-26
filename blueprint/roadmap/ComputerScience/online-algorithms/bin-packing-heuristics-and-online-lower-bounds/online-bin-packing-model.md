# Deterministic online bin packing algorithms

A **deterministic online bin-packing algorithm** with capacity $C$ is a rule that, given the items seen so far and the current bins, chooses for the next item an existing bin with room or a new bin, never moving items afterwards. Equivalently, its packing of a prefix is a function of that prefix. Two structural facts hold for every such rule: the packing of $\ell_1 \ell_2$ extends the packing of $\ell_1$, and items failing a predicate never change the number of bins holding an item satisfying it. First Fit is an online algorithm. The **asymptotic competitive ratio** is $\limsup_{\mathrm{OPT} \to \infty} \sup (\text{bins used}/\mathrm{OPT})$.

## Depends on

- [Packings and the volume bound](packings-and-volume-bound.md)

## Sources

- A. C.-C. Yao, "New Algorithms for Bin Packing", Journal of the ACM 27(2), 1980.
- J. Balogh, J. Békési, G. Dósa, L. Epstein and A. Levin, "A New and Improved Algorithm for Online Bin Packing", 26th European Symposium on Algorithms (ESA), 2018.
