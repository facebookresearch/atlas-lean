# Trace family of a concept class on a finite sample

For a binary concept class $C$ of functions $\alpha \to \{\text{true},\text{false}\}$ and a finite sample $s \subseteq \alpha$, the trace family $C|_s$ is the finite family of subsets $t \subseteq s$ (subsets of the sample itself) that are realized as positive sets by some concept:

$$C|_s = \{\, t \subseteq s : \exists c \in C,\ \forall x \in s,\ (x \in t \iff c(x) = \text{true}) \,\}.$$

Concepts that agree on $s$ contribute a single trace, and labels outside $s$ play no role.
