# Receiver transitions of the alternating-bit protocol with data

The transitions of each
receiver state, as a list of pairs of a label and a successor state, for bits $b$ and $d$:
$\mathsf{expect}(b)$ inputs on $\mathsf{recv}(b, d)$ and moves to $\mathsf{deliver}(b, d)$, or
inputs a duplicate on $\mathsf{recv}(\lnot b, d)$ and moves to the state $\mathsf{reply}(\lnot b)$,
these two for $d = \mathrm{false}$ and then for $d = \mathrm{true}$; $\mathsf{deliver}(b, d)$
outputs on $\mathsf{del}(d)$ and moves to the state $\mathsf{reply}(b)$; and the state
$\mathsf{reply}(b)$ outputs on the channel $\mathsf{reply}(b)$ and moves to
$\mathsf{expect}(\lnot b)$. So the receiver delivers the data of an expected frame and
acknowledges a duplicate again.
