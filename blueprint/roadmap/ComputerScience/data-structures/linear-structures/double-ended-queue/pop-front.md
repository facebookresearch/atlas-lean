# Pop the front of a deque

Let $d$ be a deque with front list $f$ and back list $b$, where
$b$ is stored in reverse order. If $f$ has first element $v$ and remaining list $f'$, popping the
front of $d$ returns $v$ together with the deque with front list $f'$ and back list $b$. If $f$ is
empty and the reverse of $b$ has first element $v$ and remaining list $r$, it returns $v$ together
with the deque with front list $r$ and empty back list. If both lists are empty, it returns no
result.
