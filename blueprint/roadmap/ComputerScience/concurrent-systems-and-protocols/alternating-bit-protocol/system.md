# The alternating-bit protocol in a configuration

Consider a configuration with sender
state $s$, data channel state $d$, receiver state $r$ and acknowledgement channel state $k$.
Write $\mathrm{Sender}(s)$, $\mathrm{Data}(d)$, $\mathrm{Receiver}(r)$ and $\mathrm{Ack}(k)$
for the constants of the four agents at these states, and let $L$ be the set of internal
channels $\mathrm{send}(b)$, $\mathrm{recv}(b)$, $\mathrm{reply}(b)$ and $\mathrm{ack}(b)$ for
both bits $b$. The protocol process is the parallel composition of these constants with every
internal channel restricted,
$(((\mathrm{Sender}(s) \mid \mathrm{Data}(d)) \mid \mathrm{Receiver}(r)) \mid \mathrm{Ack}(k))
\setminus L$.
