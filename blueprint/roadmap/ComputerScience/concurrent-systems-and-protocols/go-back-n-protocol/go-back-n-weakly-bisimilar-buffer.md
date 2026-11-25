# Go-back-N with window 2 implements a two-place buffer

In the labelled transition system of the go-back-N specification, the
[go-back-N protocol](go-back-n.md) with window size $2$ and sequence numbers modulo $3$, in its initial
configuration (over a lossy one-place data channel, with timeouts and cumulative acknowledgements), is weakly
bisimilar to the empty two-place buffer.
