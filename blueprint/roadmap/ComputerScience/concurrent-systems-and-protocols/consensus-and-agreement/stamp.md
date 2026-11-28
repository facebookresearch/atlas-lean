# Stamp

The maximum of zero and the round numbers of all `ack p` events strictly before `t`.
This is a prefix maximum even on an arbitrary stream. On a program prefix, ACKs by `p` are
ordered adoptions, so it equals the most recent adoption round, or zero if there was none.
