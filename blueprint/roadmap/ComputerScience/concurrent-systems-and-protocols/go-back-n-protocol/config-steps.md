# Transitions of go-back-N configurations

The transitions of a go-back-N configuration
(sender, data channel, receiver) are those of the parallel composition of the three components,
in which one component moves alone or two components synchronize on complementary labels in a
silent step, restricted to the silent steps and the steps whose label is not on an internal
channel ($\mathsf{send}_k$, $\mathsf{recv}_k$ or $\mathsf{ack}_k$ for $k \in \{0, 1, 2\}$).
