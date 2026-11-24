# A Boolean input is a threshold of its spread

For every Boolean input $v$ on $n$ wires,
applying the threshold map that sends a natural number $k$ to true if $n \le k$ and to false
otherwise to the spread of $v$ gives back $v$: for every wire $i$, the spread of $v$ at $i$ is at
least $n$ exactly when $v(i)$ is true.

Since the threshold map is monotone, $v$ is a monotone image of its spread.
