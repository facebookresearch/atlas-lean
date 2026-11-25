# Pop the back of a deque

Let $d$ be a deque with front list $f$ and back list $b$, where
$b$ is stored in reverse order. If $b$ has first element $v$ and remaining list $b'$, popping the
back of $d$ returns $v$ together with the deque with front list $f$ and back list $b'$. If $b$ is
empty and the reverse of $f$ has first element $v$ and remaining list $r$, it returns $v$ together
with the deque with empty front list and back list $r$. If both lists are empty, it returns no
result.
