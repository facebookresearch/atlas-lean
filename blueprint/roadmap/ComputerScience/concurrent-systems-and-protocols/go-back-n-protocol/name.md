# Channel names of go-back-N

The channel names of the go-back-N protocol are
$\mathsf{acc}$ (accept a message from the user), $\mathsf{del}$ (deliver a message to the user)
and, for every natural number $k$: $\mathsf{send}\,k$ (sender to data channel, a frame with
sequence number $k$), $\mathsf{recv}\,k$ (data channel to receiver), $\mathsf{ack}\,k$ (receiver
to sender, the cumulative acknowledgement naming $k$ as the next expected frame) and
$\mathsf{reply}\,k$ (receiver to the acknowledgement channel, in the lossy variant).

The protocol only uses the sequence numbers $0$, $1$ and $2$.
