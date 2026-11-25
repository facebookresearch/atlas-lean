# Composition of action signatures

Let $S_1$ and $S_2$ be [strongly compatible](strongly-compatible.md) action signatures. Their composition $S_1 \cdot S_2$ (Lynch and Tuttle, 1989, §3.2) is the action signature with outputs the outputs of either component, internal actions the internal actions of either, and inputs the inputs of either that are output by neither:

$$\mathrm{out}(S_1 \cdot S_2) = \mathrm{out}(S_1) \cup \mathrm{out}(S_2), \quad \mathrm{int}(S_1 \cdot S_2) = \mathrm{int}(S_1) \cup \mathrm{int}(S_2), \quad \mathrm{in}(S_1 \cdot S_2) = (\mathrm{in}(S_1) \cup \mathrm{in}(S_2)) \setminus (\mathrm{out}(S_1) \cup \mathrm{out}(S_2)).$$

Strong compatibility makes these three sets pairwise disjoint.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: §3.2.
