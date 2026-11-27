# Peek at the front of a deque

Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Peeking at the front of $d$ returns, without removing it,
the first element of $f$ when $f$ is nonempty, and otherwise the last element of $b$; when both
lists are empty it returns no element.
