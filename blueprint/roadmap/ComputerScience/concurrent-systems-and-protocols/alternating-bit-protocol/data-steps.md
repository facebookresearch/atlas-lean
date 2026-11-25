# Alternating-bit data channel transitions

The one-place data channel of the
alternating-bit protocol has the following transitions. When empty, it can input on
$\mathit{send}_b$ and become full with bit $b$, for each bit $b$. When full with bit $b$, it can
output on $\mathit{recv}_b$ and become empty, or lose the bit by a silent step and become empty.
