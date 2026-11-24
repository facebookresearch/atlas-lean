# Alternating-bit configuration transitions

The transitions of a configuration of the
alternating-bit protocol, listed as pairs of a label and a successor configuration, are obtained
by composing the transitions of the sender, the data channel, the receiver and the
acknowledgement channel in parallel, in that order (at each stage either side moves alone, or
the two sides synchronize on an input and the complementary output on the same channel name,
giving a silent step), and then keeping only the silent steps and the steps whose channel name
is not one of the internal channel names.
