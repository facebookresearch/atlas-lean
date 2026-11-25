# Running a sequence of queue operations

Running a list of queue operations from a
queue $q$ performs the operations one step at a time from left to right, starting at $q$.
The result is the final queue, and the cost is the sum of the costs of the individual
steps; running the empty list returns $q$ at cost $0$.
