# Periodic task model

A periodic task has a positive integer run time and period, and starts at a nonnegative integer phase. Its requests are released one period apart and each must finish by the next release. A run time larger than the period is allowed in the model.

## Idea

The model separates the release pattern from the scheduling rule. The release pattern fixes each request’s deadline; the schedule determines when work is received and whether any request misses its deadline.

## Statements

- [Periodic tasks](periodic-task.md)
- [Work received by a request](received-work.md)
- [Pending requests](is-live.md)
- [The first overflow of a schedule](first-overflow.md)
- [Response time of a request](response-time.md)
- [Fixed-priority rules](is-fixed-priority.md)
- [The deadline-driven priority rule](deadline-rule.md)
- [Preemptive priority-driven schedules](produce-schedule.md)
- [Processor utilization of a task set](utilization.md)
- [Hyperperiod of a task set](hyperperiod.md)
- [Feasibility needs every run-time to be at most its period](run-time-le-period.md)
- [Feasibility of a single periodic task](feasible-produce-schedule-iff-of-unique.md)
