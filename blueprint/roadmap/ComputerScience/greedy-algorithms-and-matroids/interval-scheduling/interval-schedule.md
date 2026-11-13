# Earliest-finish greedy interval scheduling

Given start and finish times $s$ and $f$ in a
linear order and a list $L$ of activities, sort $L$ by finish time with merge sort, then scan the
sorted list: the first activity is selected, and each later activity $a$ is selected exactly when
$s(a)$ is at least the finish time of the last selected activity. The result is the list of
selected activities in sorted order, together with a cost that counts one for each finish-time
comparison made by the merge sort and one for each scanned activity after the first.
