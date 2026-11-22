# The stuck lossy go-back-N configuration refuses new messages

Consider go-back-N with a
lossy acknowledgement channel in the configuration where the sender's window has base $0$ with two
outstanding messages, both transmitted (offset of the next frame $2$), the data channel and the
acknowledgement channel are empty, and the receiver holds frame $1$ about to deliver it. This
process has no weak transition labelled by accepting a message: no sequence of silent steps
followed by an accept input and further silent steps is possible from it.
