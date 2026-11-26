# Applying an event to a configuration

Let `e` be an event of process `p` delivering the
multiset `A` of messages, each paired with its sender, in the configuration `C`, and let `(q, B)`
be the value of the transition function of `p` at its state in `C` and `A`. The event removes from
each channel `chan i p` the messages of `A` sent by `i`, sets the state of `p` to `q`, and adds to
each channel `chan p j` the messages of `B` for `j`.
