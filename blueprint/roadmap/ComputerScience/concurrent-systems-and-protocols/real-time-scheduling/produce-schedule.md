# Preemptive priority-driven schedules

A priority rule gives each request `k` of each task
`i` a priority `rule i k` in a linearly ordered type, a smaller value being a higher priority. The
priority-driven schedule of the rule runs in each slot `t` the task of the live request of highest
priority, ties between equal priorities being broken by the least task index, and leaves slot `t`
idle only when no request is live at `t`. A request is live at `t` if it has been made, its
deadline has not passed and it has received fewer than `C` slots of work before `t`, so a request
whose deadline passes before it receives `C` slots is dropped. Whenever a task of higher priority
than the running one is requested, the running task is thus interrupted at once and the requested
task started: this is a preemptive, priority-driven scheduling algorithm in the sense of Liu and
Layland, and it is feasible for a task set if this schedule is feasible.
