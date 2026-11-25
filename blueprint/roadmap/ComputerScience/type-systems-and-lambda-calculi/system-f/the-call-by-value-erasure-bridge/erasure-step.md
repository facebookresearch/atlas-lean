# Erasure of a System F evaluation step is a beta conversion

Let $t, t' \in \mathrm{Tm}_{n,m}$ with $t \to t'$ ([call-by-value step](../call-by-value-safety-for-pure-system-f/step.md)). For every assignment $\sigma$ of terms of the untyped term model to the $m$ term variables, the [closings](../system-f-erasure-and-closing-environments/close.md) $t\{\sigma\}$ and $t'\{\sigma\}$ are [β-equivalent](../the-existing-untyped-beta-conversion-term-model/beta-eq.md).
