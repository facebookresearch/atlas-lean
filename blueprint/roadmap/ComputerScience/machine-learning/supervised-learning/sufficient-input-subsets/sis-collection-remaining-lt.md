# Masking the SIS-collection leaves the prediction below the threshold

**Proposition 2** of Carter et al.: let $g$ be a real function on the finite subsets of a set of
features, $\tau \in \mathbb{R}$ a threshold with $g(\emptyset) < \tau$, and $\pi$ a rule choosing
an element of every nonempty finite set. For every finite set $R$, masking every set of the
[SIS-collection](sis-collection.md) $S_1, \dots, S_r$ from $R$ leaves the prediction below the
threshold: $g\big(R \setminus (S_1 \cup \dots \cup S_r)\big) < \tau$.
