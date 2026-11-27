# Recursive CCS specification of go-back-N

The specification assigns to every process
constant the choice, over the transitions listed for its state, of the prefixes $a.K$, where $a$
is the label of the transition and $K$ is the process constant for its target state; an empty
list gives the inactive process. The constants are those of the sender, the data channel, the
receiver, the two-place buffer, the acknowledgement channel and the receiver of the lossy
variant, and their transitions are the sender steps, data channel steps, receiver steps, buffer
steps, acknowledgement channel steps and lossy receiver steps respectively.
