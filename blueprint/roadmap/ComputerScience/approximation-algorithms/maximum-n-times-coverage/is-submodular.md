# Submodular set function

A real-valued function $f$ on the finite subsets of a set $A$ is submodular when, for all finite
sets $S \subseteq T \subseteq A$ and every $x \in A \setminus T$,

$$f(T \cup \{x\}) - f(T) \le f(S \cup \{x\}) - f(S):$$

adding an element to a larger set gains at most as much as adding it to a smaller set (the
diminishing-returns form of Definition 2 of Liu et al.).

## Sources

- G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine design", *International Conference on Learning Representations (ICLR)*, 2022, arXiv:2101.10902, §2.2, Appendix A, Definition 2.
