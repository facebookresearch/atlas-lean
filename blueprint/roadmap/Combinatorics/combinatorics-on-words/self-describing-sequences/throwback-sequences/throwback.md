# Throwback operation

Let $s = (s_0, s_1, s_2, \dots)$ be a sequence of elements of a set
$A$, each element $a$ carrying a weight $w(a) \in \mathbb{N}$. The throwback $\tau_w(s)$ moves the
leader $s_0$ to index $w(s_0)$, moves the entries at indices $1, \dots, w(s_0)$ one place left and
leaves later entries in place: $\tau_w(s)_i = s_{i+1}$ for $i < w(s_0)$,
$\tau_w(s)_{w(s_0)} = s_0$, and $\tau_w(s)_i = s_i$ for $i > w(s_0)$.

With $A = \mathbb{N}$ and $w$ the identity, this is the throwback $\tau$ of Darnell and Dribus on
sequences of positive integers. With $A = \mathbb{N}$, the initial arrangement $s_i = i$ and
weights $w(i) = x_i$ for a sequence $X = (x_0, x_1, \dots)$, it tracks the original index of each
term, so repeated values stay distinguishable.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 2.
