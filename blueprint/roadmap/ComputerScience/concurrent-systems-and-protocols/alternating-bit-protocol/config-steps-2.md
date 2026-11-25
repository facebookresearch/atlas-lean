# Transitions of the alternating-bit protocol with data

For a configuration, made of a
sender state, a data-channel content, a receiver state and an acknowledgement-channel content,
the transitions are those of the parallel composition of the sender, the data channel, the
receiver and the acknowledgement channel, where one component moves alone or two components
synchronize on complementary labels in a silent step. Of these, only the silent steps and the
actions on names that are not internal channels are kept; the internal channels are the sending,
receiving, reply and acknowledgement channels.
