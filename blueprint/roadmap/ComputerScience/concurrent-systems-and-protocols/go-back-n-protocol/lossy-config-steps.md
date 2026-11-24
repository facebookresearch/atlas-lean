# Transitions of lossy go-back-N configurations

The transitions of a configuration of
the lossy go-back-N variant come from the parallel composition of the sender, the data
channel, the lossy-variant receiver and the acknowledgement channel (in each composition
either side moves alone, or the two sides synchronize on complementary input and output
labels in a silent step), keeping only the silent transitions and those whose label is not
on an internal channel $\mathrm{send}_k$, $\mathrm{recv}_k$, $\mathrm{ack}_k$ or
$\mathrm{reply}_k$, $k \in \{0, 1, 2\}$.
