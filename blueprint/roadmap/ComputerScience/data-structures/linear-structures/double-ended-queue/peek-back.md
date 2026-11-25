# Peek at the back of a deque

Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Peeking at the back of $d$ returns, without removing it,
the first element of $b$ when $b$ is nonempty, and otherwise the last element of $f$; when both
lists are empty it returns no element.
