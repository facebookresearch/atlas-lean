# Receiver transitions of lossy go-back-N

The transitions of the receiver of the lossy
variant, as pairs of a label and a successor state, are those of the receiver of the reliable
protocol, except in the state about to acknowledge $k$: there the only transition is an output on
$\mathsf{reply}\,k$, to the acknowledgement channel, after which the receiver expects $k$.
