# Modeled cost of a dequeue

For a queue stored as an enqueue list and a dequeue list, the
modeled cost of dequeueing is $1$ when the dequeue list is nonempty, and $m + 1$ when the dequeue
list is empty, where $m$ is the length of the enqueue list (the number of elements reversed when
they are moved to the dequeue list).
