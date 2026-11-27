# Padding is injective

For every block length $B$ and length-field width $L$, distinct messages have distinct paddings, with no
bound on the message length (Katz and Lindell, Construction 5.3). Removing the length field leaves
$M 1 0 \cdots 0$, and the last $1$ bit marks the end of $M$, so the length field is never read and
$|M| \ge 2^L$ is allowed.
