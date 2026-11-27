# Worst-case absorption time of the Moran process on graphs

Is the worst expected fixation-or-extinction time on undirected n-vertex graphs of order n³ for each fixed positive r≠1? This controls evolutionary timescales and simulation cost.

## What would settle it

Prove $\exists C_r\, \forall G,\ \mathbb{E}[\tau_{\mathrm{abs}}] \le C_r n^3$, or give a graph family with a supercubic expectation. Count all Moran updates, including updates that do not change the state, rather than silently changing the time unit.

## Status

The cited sources, in the versions cited, record the partial results below; they do not pose the question in this form, and this page does not certify its present status. This status evidence is older or incomplete; check later literature before relying on it.

Goldberg, Lapinskas and Richerby prove that the expected absorption time is at most n^3 exp(O((log log n)^3)) for every positive r ≠ 1 and exhibit graphs where it is Ω(n^3).

This page records the research target above and asserts no theorem or present-status certification.

## Sources

- Leslie Ann Goldberg, John Lapinskas and David Richerby, *Phase Transitions of the Moran Process and Algorithmic Consequences*, arXiv:1804.02293v4 (2019), §1, Theorem 1. <https://arxiv.org/abs/1804.02293v4>
