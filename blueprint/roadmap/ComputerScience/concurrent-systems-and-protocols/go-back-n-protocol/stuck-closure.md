# Silent closure of the stuck lossy go-back-N configuration

The list of the seven
configurations of go-back-N with a lossy acknowledgement channel in which the sender's window has
base $0$ with two outstanding messages, the receiver holds frame $1$ about to deliver it, and the
acknowledgement channel is empty, while the sender's offset of the next frame to transmit and the
data channel are, in order: offset $2$ and empty, offset $0$ and empty, offset $1$ holding frame
$0$, offset $0$ holding frame $0$, offset $1$ and empty, offset $2$ holding frame $1$, and offset
$0$ holding frame $1$.

The first is the stuck configuration, reached after the acknowledgement of frame $0$ was lost; the
list is closed under silent steps (proved separately), so it contains every configuration
silently reachable from it.
