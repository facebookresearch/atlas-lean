# Boolean sorting test

The Boolean sorting test of a comparator network on $n$ wires
returns true exactly when, for every assignment $v$ of a Boolean value to each wire, the output
$w$ of the network on $v$ satisfies $w(i) \le w(j)$ for all wires $i \le j$, where
$\mathrm{false} < \mathrm{true}$.

It is computed by running the network on all $2^n$ Boolean inputs.
