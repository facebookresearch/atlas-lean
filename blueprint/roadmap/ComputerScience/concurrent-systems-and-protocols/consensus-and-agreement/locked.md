# Locked

The stream contains an `ack p r v` strictly before `T` for each `p` in a strict majority.
On a program prefix these occurrences record adoption of the round's suggestion and the sending
of an ACK; their receipt by the coordinator is not required.
